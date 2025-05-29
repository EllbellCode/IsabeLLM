# IsabeLLM
IsabeLLM is a tool that integrates a Large Language Model with the theorem prover [Isabelle](https://isabelle.in.tum.de) via an API.


## Installation
1. **Scala configuration**
   
    Install SDKMAN:
    ```shell
    curl -s "https://get.sdkman.io" | bash
    source .bashrc
    ```
    Install JAVA 11 and scala build tool (sbt):
    ```shell
    sdk install java 11.0.11-open
    sdk install sbt
    ```
2. **Python configuration**

   Install python:
   ```shell
   sudo apt install python3 python3-pip -y
   ```
   Install virtual environment:
   ```shell
   sudo apt install python3-venv -y
   ```
   Create and activate a virtual environment:
   ```shell
   python3 -m venv myenv
   source venv/bin/activate
   ```
3. **API configuration**

   Intall the openai library for python:
   ```shell
   pip install openai
   ```
   Setup a free [OpenRouter](https://openrouter.ai) account a create a new api key.
   Export your api key:
   ```shell
   export aikey="<YOUR API KEY>"
   ```
   
4. **Clone project and make sure it compiles**

    ```shell
    git clone https://github.com/EllbellCode/IsabeLLM.git
    cd IsabeLLM
    ```

    Then compile the project:
    ```shell
    sbt compile
    ```
   
5. **Configure Isabelle**

    Download and install isabelle2022 in the parent directory
    ```shell
    cd ~
    wget https://isabelle.in.tum.de/dist/Isabelle2022_linux.tar.gz
    tar -xzf Isabelle2022_linux.tar.gz
    alias isabelle=~/Isabelle2022/bin/isabelle
    ```
    Add the name of your theory files to the ROOT file

6. **Run IsabeLLM**

   ```shell
   sbt run
   ```

